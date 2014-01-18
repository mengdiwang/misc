//http://zh.wikipedia.org/wiki/多边形

#include <stdio.h>

struct TPoint
{
	TPoint(double ax, double ay)
	{
		x = ax;
		y = ay;
	}
	
	double x;
	double y;
};

double polygonArea(TPoint points[], int n)
{
	double area = 0;

	for(int i=1; i<=n; i++)
	{
		area += (points[i-1].x * points[i%n].y - points[i%n].x * points[i-1].y);
	}
	
	return area/2;
}

int main()
{	
	TPoint points[4] = {TPoint(0,0), TPoint(1,0),TPoint(1,1), TPoint(0,1)};
	double val = polygonArea(points, 4);
	printf("%lf",val);

	return 0;
}